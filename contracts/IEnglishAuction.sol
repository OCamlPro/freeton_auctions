pragma ton-solidity >=0.44;

import "IAuction.sol";

interface IEnglishAuction is IAuction {
    function endAuction() external;
}