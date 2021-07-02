pragma ton-solidity >=0.44;

interface IProcessWinner{
    function acknowledgeWinner(address, uint256) external;
    function acknowledgeNoWinner() external;
}
