certoraRun BankWithLoops.sol:Bank --verify Bank:Loops.spec \
--solc solc7.6 \
--send_only \
--msg "$1"


certoraRun BankWithLoops.sol:Bank --verify Bank:Loops.spec \
--solc solc7.6 \
--send_only \
--msg "$1" \
--rule sumFunds --optimistic_loop


 certoraRun BankWithLoops.sol:Bank --verify Bank:Loops.spec \
 --solc solc7.0 \
 --optimistic_loop \
 --loop_iter 2 \
 --rule whoChangedMyGhost