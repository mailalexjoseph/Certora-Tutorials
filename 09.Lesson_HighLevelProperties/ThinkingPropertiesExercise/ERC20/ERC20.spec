methods{
    totalSupply() returns (uint256) envfree
    balanceOf(address account) returns (uint256) envfree
    transfer(address recipient, uint256 amount) returns (bool)
    allowance(address owner, address spender) returns (uint256)
}

invariant UserBalanceLessThanTotalSupply(address user)
totalSupply()>=balanceOf(user)

rule totalSupplyConstant(method f){
    env e; calldataarg args;
    uint256 totalSupplyBefore = totalSupply();
    f(e,args);
    uint256 totalSupplyAfter = totalSupply();
    assert (totalSupplyAfter==totalSupplyBefore);
}

rule BalanceChangeAfterTransfer(address sender, address recipient, uint256 amount){
    env e; calldataarg args;
    require e.msg.sender == sender;
    require amount>=0;
    uint256 senderBalanceBefore; uint256 recipientBalanceBefore;
    transfer@withrevert(e, recipient,amount);
    bool success = !lastReverted;
    uint256 senderBalanceAfter; uint256 recipientBalanceAfter;
    assert(success => (senderBalanceBefore-amount == senderBalanceAfter),"sender balance did not go down by the right amount");
    assert(success => (recipientBalanceBefore+amount == recipientBalanceAfter),"recipient balance did not go up by the right amount");

}