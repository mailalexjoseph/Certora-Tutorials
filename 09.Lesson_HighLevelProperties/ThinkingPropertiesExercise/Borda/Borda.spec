methods{
    getPointsOfContender(address contender) returns(uint256) envfree
    getFullContenderDetails(address contender) returns(uint8 age, bool registered, uint256 points) envfree
    vote(address first, address second, address third) returns(bool)
    hasVoted(address voter) returns(bool) envfree
    getFullVoterDetails(address voter) returns(uint8 age, bool registered, bool voted, uint256 vote_attempts, bool black_listed)
}



rule MonotonousIncreaseInVotes(method f, address contender){
    env e; calldataarg args;
    uint8 age; bool registeredBefore; uint256 pointsBefore;
    age, registeredBefore, pointsBefore = getFullContenderDetails(contender);
    require registeredBefore;
    f(e,args);
    uint256 pointsAfter = getPointsOfContender(contender);
    assert(pointsAfter>=pointsBefore);

}

rule voterShouldVoteOnlyOnce (address voter){
    env e; calldataarg args;
    bool hasVoted = hasVoted(voter);
    // require (hasVoted);
    bool success;
    vote@withrevert(e, args);
    success = !lastReverted;
    assert(e.msg.sender == voter && hasVoted) => !success;
}

rule ContenderVoteCountUnchangedIfNotVotedFor (address first, address second, address third, address contender){
    env e; calldataarg args;
    uint256 votesBefore = getPointsOfContender(contender);
    require(contender!=first && contender!=second && contender!=third);
    vote(e, first, second, third);
    uint256 votesAfter = getPointsOfContender(contender);
    assert(votesAfter == votesBefore);
    // assert false;
}

rule BlacklistedOnThirdVotingAttempt (address first, address second, address third, address voter){
    env e; calldataarg args;
    uint8 age; bool registered; bool voted; uint256 vote_attemptsBefore; bool black_listedBefore;
    age, registered, voted, vote_attemptsBefore, black_listedBefore = getFullVoterDetails(e, voter);
    require(vote_attemptsBefore==2 && !black_listedBefore);
    vote(e, first, second, third);
    uint256 vote_attemptsAfter; bool black_listedAfter;
    age, registered, voted, vote_attemptsAfter, black_listedAfter = getFullVoterDetails(e, voter);
    assert(vote_attemptsAfter ==3,"vote attempts not incremented");
    assert(black_listedAfter,"not blacklisted on third attempt");

    // assert false;
}