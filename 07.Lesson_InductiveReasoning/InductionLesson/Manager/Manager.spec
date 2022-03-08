methods {
	getCurrentManager(uint256 fundId) returns (address) envfree
	getPendingManager(uint256 fundId) returns (address) envfree
	isActiveManager(address a) returns (bool) envfree
}


rule uniqueManagerAsRule(uint256 fundId1, uint256 fundId2, method f) {
	// assume different IDs
	require fundId1 != fundId2;
	// assume different managers
	address managerBefore1 = getCurrentManager(fundId1);
	address managerBefore2 = getCurrentManager(fundId2);
	bool managerBefore1Active = isActiveManager(managerBefore1);
	bool managerBefore2Active = isActiveManager(managerBefore2);
	require managerBefore1 != managerBefore2;
	
	require (managerBefore1!=0 => managerBefore1Active);
	require (managerBefore2!=0 => managerBefore2Active);
	
	
	// hint: add additional variables just to look at the current state
	// bool active1 = isActiveManager(getCurrentManager(fundId1));			
	
	env e;
	calldataarg args;
	
	if (f.selector == claimManagement(uint256).selector)
	{
		uint256 id;
		require (id == fundId1 || id == fundId2);
		claimManagement(e, id);  
	}
	else f(e,args);
	

	address managerAfter1 = getCurrentManager(fundId1);
	address managerAfter2 = getCurrentManager(fundId2);
	// verify that the managers are still different 
	assert managerAfter1 != managerAfter2, "managers not different";
	assert managerAfter1 != 0 => isActiveManager(managerAfter1), "manager1 is not active";
	assert managerAfter2 != 0 => isActiveManager(managerAfter2), "manager2 is not active";
}


/* A version of uniqueManagerAsRule as an invariant */
invariant uniqueManagerAsInvariant(uint256 fundId1, uint256 fundId2)
	fundId1 != fundId2 => getCurrentManager(fundId1) != getCurrentManager(fundId2) 

