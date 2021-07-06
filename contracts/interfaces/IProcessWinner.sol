pragma ton-solidity >=0.44;

import "IConstants.sol";

interface IProcessWinner is IConstants{
    function acknowledgeWinner(Bidder) external;
    function acknowledgeNoWinner() external;
}
