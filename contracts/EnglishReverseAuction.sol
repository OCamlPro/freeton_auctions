pragma ton-solidity >=0.44;

import "VEnglishAuction.sol";
import "Constants.sol";
import "IEnglishAuction.sol";

contract EnglishReverseAuction is Constants, IEnglishAuction, VEnglishAuction {
    function newBidIsBetterThan(uint128 b) internal override returns (bool){
        return (msg.value < b);
    }
}