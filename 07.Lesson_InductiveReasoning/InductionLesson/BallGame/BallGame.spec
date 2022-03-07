
methods {
	ballAt() returns uint256 envfree
}

invariant neverReachPlayer4() 
	ballAt() != 4 
	
rule neverReachPlayer4Parametric(method f) {
env e;
uint stateBefore = ballAt();
require(stateBefore==1);
f(e);
uint stateAfter = ballAt();
assert(stateAfter!=4);
}	
