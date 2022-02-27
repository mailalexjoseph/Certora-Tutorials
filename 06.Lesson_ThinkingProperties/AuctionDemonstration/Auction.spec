/* Certora prover verifies calls for all environments. 
   The environment is passed as an additional parameter to functions.
   It can be seen as the following structure, paralleling solidity definitions:
   
    struct env {
         address msg.address // address of the contract being verified
         address msg.sender //  address of the sender of the message 
         uint msg.value  // number of wei sent with the message
         uint block.number // current block number
         uint block.timestamp // current timestamp
         address tx.origin // original transaction sender
    }
    
    An `envfree` method is one that is:
    (1) non-payable (msg.value must be 0)
    (2) does not depend on any environment variable
*/

// @note Valid States for an auction:
// INACTIVE: when an auction is uninitialized or has been closed. All the variables (prize, amount, winner, bid_expiry and end_time) are 0
// OPEN: when the auction has been initialized by the owner starting with a prize of MAX_UINT256, amount>0, winner!=0, bid_expiry=0, end_time!=0
// BID_PLACED: when one or more bids have been placed on an open auction with prize <MAX_UINT256, amount>0, winner!=0, bid_expiry!=0, end_time!=0
// INVALID: any state other than the above is invalid

methods {
    getTotalSupply() returns uint256 envfree
    balanceOf(address) returns uint256 envfree
    getAuction(uint) returns (uint,uint,address,uint,uint) envfree
}


function getPrize (uint id) returns uint{
    uint prize; uint payment; address winner; uint bid_expiry; uint end_time;
    prize, payment, winner, bid_expiry, end_time = getAuction(id);
    return prize;
}



// definition MAX_UINT256() returns uint256 = 0xffffffffffffffffffffffffffffffff;

definition INACTIVE() returns uint = 0;
definition OPEN() returns uint = 1;
definition BID_PLACED() returns uint = 2;
definition INVALID() returns uint = 3;

function auctionState(uint id) returns uint{
uint prize; uint payment; address winner; uint bid_expiry; uint end_time;
    prize, payment, winner, bid_expiry, end_time = getAuction(id);

if (prize ==0 && payment ==0 && winner==0 && bid_expiry==0 && end_time==0){ return 0;}
else if(prize==max_uint && payment>0 && winner!=0 && bid_expiry==0 && end_time!=0) {return 1;}
else if(prize<max_uint && payment >0 && winner!=0 && bid_expiry!=0 && end_time!=0) {return 2;}
else return 3;
}


//@note **************** My rules ***********************/

//@note checking for valid state transitions out of the INACTIVE state and function used for transition
rule InactiveStateTransition(method f, uint id){
    env e;
    calldataarg args;
    uint stateBefore = auctionState(id);
    f(e, args);
    uint stateAfter = auctionState(id);
    assert(stateBefore==INACTIVE() => (stateAfter==INACTIVE() || stateAfter==OPEN()),"Invalid state transition");
    assert((stateBefore==INACTIVE() && stateAfter==OPEN()) => f.selector==newAuction(uint, uint).selector,"new aunction started by a function other than newAuction()");
}

// // @note checking for valid state transitions out of the OPEN state and the function used for transition
// rule OpenStateTransition(method f, uint id){
//     env e;
//     calldataarg args;
//     uint stateBefore = auctionState(id);
//     f(e, args);
//     uint stateAfter = auctionState(id);
//     assert(stateBefore==OPEN() => (stateAfter==INACTIVE() || stateAfter==OPEN() || stateAfter==BID_PLACED()),"Invalid state transition");
//     assert((stateBefore==OPEN() && stateAfter==BID_PLACED()) => f.selector==bid(uint, uint).selector,"Bid placed by a function other than bid()");
//     assert((stateBefore==OPEN() && stateAfter==INACTIVE()) => f.selector==close(uint).selector),"aunction closed by a function other than close()";
// }

// // @note checking for valid state transitions out of the BID_PLACED state and close() function used for transition
// rule BidPlacedStateTransition(method f, uint id){
//     env e;
//     calldataarg args;
//     uint stateBefore = auctionState(id);
//     f(e, args);
//     uint stateAfter = auctionState(id);
//     assert(stateBefore==BID_PLACED() => (stateAfter==BID_PLACED() || stateAfter==INACTIVE()),"Invalid state transition");
//     assert((stateBefore==BID_PLACED() && stateAfter==OPEN()) => f.selector==close(uint).selector,"aunction closed by a function other than close()");
// }

// // @note checking if any function execution causes an auction to reach an invalid state
// rule ValidState(method f, uint id){
//     env e;
//     calldataarg args;
//     uint stateBefore = auctionState(id);
//     f(e, args);
//     uint stateAfter = auctionState(id);
//     assert(stateBefore!=INVALID() => stateAfter!=INVALID(),"Reach invalid state");
// }

rule monotonousDecreasingPrize(method f, uint id){
env e;
calldataarg args;
uint prizeBefore = getPrize(id);
f(e, args);
uint prizeAfter = getPrize(id);
assert(prizeAfter< prizeBefore,"prize cannot increase");
}


/**************** Generic rules ***********************/
// A rule for verifying that the total supply stays less than MAX_UINT256
rule boundedSupply(method f) {
    // Fetch total supply before
    uint256 _supply = sinvoke getTotalSupply(); 
    
    // Invoke an arbitrary public function on an arbitrary input and take into account only cases that do not revert
    env e; // For every possible environment 
    calldataarg arg;
    sinvoke f(e,arg);
    
    // Fetch total supply after
    uint256 supply_ = sinvoke getTotalSupply(); 
    
    assert _supply != supply_ => 
        supply_ < 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 
        "Cannot increase to MAX_UINT256";   
}

// A rule for verifying that any scenario preformed by some sender does not decrease the balance of any other account.
rule senderCanOnlyIncreaseOthersBalance(method f, address sender, address other)
{  
    // Assume we have two different accounts.
    require other != sender; 
    
    // Get the current balance of the other account
    uint256 origBalanceOfOther = sinvoke balanceOf(other); 

    // Invoke any function with msg.sender being the sender account
    calldataarg arg;
    env ef;
    require ef.msg.sender == sender;
    invoke f(ef, arg);

    uint256 newBalanceOfOther = sinvoke balanceOf(other);

    assert newBalanceOfOther >= origBalanceOfOther, 
        "The balance of the other account decreased"; 
}

// A rule for verifying a correct behavior on sending zero tokens - return false or revert 
rule transferWithIllegalValue(address to)
{
    // Assume the case that `to` is not zero
    require to != 0; 

    env e; // For every possible environment
    // Assume no `msg.value` since this `transferTo` not a payable function
    require e.msg.value == 0; 
    bool res = invoke transferTo(e, to, 0);

    assert lastReverted || !res, 
        "permits a transfer of zero tokens";
}




