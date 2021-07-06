pragma ton-solidity >=0.44;

import "Constants.sol";

interface IProcessWinner is IConstants{
    function acknowledgeWinner(Bidder) external;
    function acknowledgeNoWinner() external;
}
