pragma ton-solidity >=0.44;

import "VEnglishAuction.sol";
import "Constants.sol";
import "interfaces/IAuction.sol";

contract EnglishReverseAuction is Constants, IAuction, VEnglishAuction {
    function newBidIsBetterThan(uint256 old_bid, uint256 new_bid) internal override returns (bool){
        return (new_bid < old_bid);
    }
}