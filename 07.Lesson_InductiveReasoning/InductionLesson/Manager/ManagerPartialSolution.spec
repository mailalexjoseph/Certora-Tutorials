methods {
		getCurrentManager(uint256 fundId) returns (address) envfree
		getPendingManager(uint256 fundId) returns (address) envfree
		isActiveManager(address a) returns (bool) envfree
}



rule uniqueManager(uint256 fundId1, uint256 fundId2, uint256 fundId3, method f) {
	// @note adding a separate fundId variable for createFund() since it requires uninitialized funds. 
	// Preconditions written with claimManagement() in mind will always lead to revert in the createFund() function.
	// The will give a false positive for createFunds().
	require fundId1 != fundId2;
	require fundId3 != fundId2;
	require getCurrentManager(fundId3) == 0 ;
	require getCurrentManager(fundId1) != 0 && isActiveManager(getCurrentManager(fundId1));
	require getCurrentManager(fundId2) != 0 && isActiveManager(getCurrentManager(fundId2));
	require getCurrentManager(fundId1) != getCurrentManager(fundId2) ;
				
	env e;
	if (f.selector == claimManagement(uint256).selector)
	{
		uint256 id;
		require id == fundId1 || id == fundId2;
		claimManagement(e, id);  
	
		assert getCurrentManager(fundId1) != getCurrentManager(fundId2), "managers not different";
		assert getCurrentManager(fundId1) != 0 && isActiveManager(getCurrentManager(fundId1)), "manager of fund1 is not active";
		assert getCurrentManager(fundId2) != 0 && isActiveManager(getCurrentManager(fundId2)), "manager of fund2 is not active";
	}
	else {
		uint256 id;
		require id == fundId3;
		createFund(e,id);
	
		assert getCurrentManager(fundId3) != getCurrentManager(fundId2), "createFund: managers not different";
		assert getCurrentManager(fundId3) != 0 && isActiveManager(getCurrentManager(fundId3)), "manager of fund3 is not active";
	}
	// else {
	// 	calldataarg args;
	// 	f(e,args);
	// }

	

	
}