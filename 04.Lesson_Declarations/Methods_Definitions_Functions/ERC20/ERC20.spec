methods{
	name() returns (string memory) envfree
	symbol() returns (string memory) envfree
	decimals() returns (uint8) envfree
	decreaseAllowance(address spender, uint256 subtractedValue) returns (bool)
	totalSupply() returns (uint256) envfree
	balanceOf(address account) returns (uint256) envfree
	transfer(address recipient, uint256 amount) returns (bool)
	allowance(address owner, address spender) returns (uint256) envfree
	approve(address spender, uint256 amount) returns (bool)
	transferFrom(address sender, address recipient, uint256 amount) returns (bool)
	increaseAllowance(address spender, uint256 addedValue) returns (bool)
	}


/* f.selecor

 * On the right side of the implication above we see a f.selector.
 * The use of f.selector is very similar to its use in solidity -
 * since f is a parametric method that calls every function in contract in parallel,
 * we specify (or selecting) to address one particular path - when the f.selector was scheduleMeeting.
 */

// Checks that the sum of sender and recipient accounts remains the same after transfer(), i.e. assets doesn't disappear nor created out of thin air
rule integrityOfTransfer(address recipient, uint256 amount) {
	env e;
	uint256 balanceSenderBefore = balanceOf(e.msg.sender);
	uint256 balanceRecipientBefore = balanceOf(recipient);
	transfer(e, recipient, amount);
	uint256 balanceSenderAfter = balanceOf(e.msg.sender);
	uint256 balanceRecipientAfter = balanceOf(recipient);

	assert balanceRecipientBefore + balanceSenderBefore == balanceSenderAfter + balanceRecipientAfter, "the total funds before and after a transfer should remain the constant";
}


// Checks that transferFrom() correctly decrease allowance of e.msg.sender
rule integrityOfTransferFrom(address owner, address recipient, uint256 amount) {
	env e;
    require owner != recipient; // why is that necessary? try commenting this line out and see what happens
	uint256 allowanceBefore = allowance(owner, e.msg.sender);
	transferFrom(e, owner, recipient, amount);
	uint256 allowanceAfter = allowance(owner, e.msg.sender);
    
	assert allowanceBefore >= allowanceAfter, "allowance musn't increase after using the allowance to pay on behalf of somebody else";
}


// Checks that increaseAllowance() increases allowance of spender
rule integrityOfIncreaseAllowance(address spender, uint256 amount) {
	env e;
	uint256 allowanceBefore = allowance(e.msg.sender, spender);
	increaseAllowance(e, spender, amount);
	uint256 allowanceAfter = allowance(e.msg.sender, spender);

	assert amount > 0 => (allowanceAfter > allowanceBefore), "allowance did not increase";
	assert amount == 0 => (allowanceAfter == allowanceBefore), "allowance stayed the same for 0 amount";
    // Can you think of a way to strengthen this assert to account to all possible amounts?
}


// Users' balance can be changed only as a result of transfer(), transderFrom(), mint(), burn()
rule balanceChangesFromCertainFunctions(method f, address user){
    env e;
    calldataarg args;
    uint256 userBalanceBefore = balanceOf(user);
    f(e, args);
    uint256 userBalanceAfter = balanceOf(user);

    assert userBalanceBefore != userBalanceAfter => 
        (f.selector == transfer(address, uint256).selector ||
         f.selector == transferFrom(address, address, uint256).selector),
         "user's balance changed as a result function other than transfer(), transderFrom(), mint(), burn()";
}

/* possible exercise to understand why it fails */
// // Checks that the totalSupply of the token is at least equal to a single user's balance
// rule totalSupplyNotLessThanSingleUserBalance(method f, address user) {
// 	env e;
// 	calldataarg args;
// 	uint256 totalSupplyBefore = totalSupply(e);
//     uint256 userBalanceBefore = balanceOf(e, user);
//     require totalSupplyBefore >= userBalanceBefore;
//     f(e, args);
//     uint256 totalSupplyAfter = totalSupply(e);
//     uint256 userBalanceAfter = balanceOf(e, user);

// 	assert totalSupplyAfter >= userBalanceAfter, "msg";
// }