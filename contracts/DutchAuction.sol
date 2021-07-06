pragma ton-solidity >=0.44;

import "VDutchAuction.sol";
import "Constants.sol";
import "interfaces/IAuction.sol";

contract DutchAuction is Constants, IAuction, VDutchAuction {
    function betterPriceThanCurrent(uint256 b) internal override returns (bool){
        // Todo: CHECK OVERFLOW
        uint256 current_price = s_starting_price - s_price_delta * (now - s_auction_start) / s_time_delta;
        if (current_price < s_limit_price) {
            current_price = s_limit_price;
        } 
        return (b >= current_price);
    }
}