methods{
deposit()
withdraw(uint)
collectFees()
OwnerDoItsJobAndEarnsFeesToItsClients()
assetsOf(address user) returns(uint) envfree
getTotalFeesEarnedPerShare()returns(uint256) envfree
getFeesCollectedPerShare(address user)returns(uint256) envfree
getBalance(address user) returns (uint)
balanceOf(address account) returns (uint256) envfree
totalSupply() returns (uint256) envfree
}

invariant ContractETHBalanceGETotalSupply(env e)
e.msg.address.balance >= totalSupply()

rule UserETHBalanceIncreaseAfterCollect(address user, uint amount){
env e;
calldataarg args;
uint256 UserETHBalanceBefore = getBalance(e, user);
uint256 UserBalanceBefore = balanceOf(user);
collectFees(e   );
uint256 UserETHBalanceAfter = getBalance(e, user);
uint256 UserBalanceAfter = balanceOf(user);
assert(UserBalanceAfter<UserBalanceBefore => UserETHBalanceAfter>UserETHBalanceBefore);
}

rule UserETHBalanceIncreaseAfterWithdraw(address user, uint amount){
env e;
calldataarg args;
uint256 UserETHBalanceBefore = getBalance(e, user);
uint256 UserBalanceBefore = balanceOf(user);
withdraw(e, amount);
uint256 UserETHBalanceAfter = getBalance(e, user);
uint256 UserBalanceAfter = balanceOf(user);
assert(UserBalanceAfter<UserBalanceBefore => UserETHBalanceAfter>UserETHBalanceBefore);
}

rule TotalFeesEarnedPerShareMonotonousIncrease(method f){
env e;
calldataarg args;
uint256 TotalFeesPerShareBefore = getTotalFeesEarnedPerShare();
f(e, args);
uint256 TotalFeesPerShareAfter = getTotalFeesEarnedPerShare();

assert (TotalFeesPerShareAfter>=TotalFeesPerShareBefore);

}

rule FeesCollectedPerShareMonotonousIncrease(method f, address user){
env e;
calldataarg args;
uint256 FeesCollectedPerShareBefore = getFeesCollectedPerShare(user);
f(e, args);
uint256 FeesCollectedPerShareAfter = getFeesCollectedPerShare(user);

assert (FeesCollectedPerShareAfter>=FeesCollectedPerShareAfter);

}

