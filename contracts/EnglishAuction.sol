pragma ton-solidity >=0.44;

import "VEnglishAuction.sol";
import "Constants.sol";

contract EnglishAuction is Constants, VEnglishAuction {
    function newBidIsBetterThan(uint128 b) internal override returns (bool){
        return (msg.value > b);
    }
}