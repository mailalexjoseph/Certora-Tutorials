methods{
    add_liquidity() public returns (uint)
    remove_liquidity(uint LP_tokens)
    swap(address from_token)
    getContractAddress() returns (address)
    getToken0DepositAddress() returns (address) envfree
    getToken1DepositAddress() returns (address) envfree

}

rule tokenAmountsMoveTogetherForCertainFunctions(method f){
    uint256 token0AmountBefore = token0Amount();
    uint256 token1AmountBefore = token1Amount();
    calldataarg args;
    env e;
    f(args, env e);
    uint256 token0AmountAfter = token0Amount();
    uint256 token1AmountAfter = token1Amount();
    assert ((f.selector != swap(address) && token0AmountAfter>token0AmountBefore) => token1AmountAfter> token1AmountBefore);
    assert ((f.selector != swap(address) && token0AmountAfter<token0AmountBefore) => token1AmountAfter< token1AmountBefore);
    assert ((f.selector == swap(address) && token0AmountAfter<token0AmountBefore) => token1AmountAfter> token1AmountBefore);
    assert ((f.selector == swap(address) && token0AmountAfter>token0AmountBefore) => token1AmountAfter< token1AmountBefore);
}

