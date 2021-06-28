pragma ton-solidity >=0.44;

import "IAuction.sol";

interface IDutchAuction is IAuction {
    function endAuction() external;
}