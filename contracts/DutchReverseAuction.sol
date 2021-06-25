pragma ton-solidity >=0.44;

import "VDutchAuction.sol";
import "Constants.sol";
import "IDutchAuction.sol";

contract DutchReverseAuction is Constants, IDutchAuction, VDutchAuction {
    function betterPriceThanCurrent(uint128 b) internal override returns (bool){
        // Todo: CHECK OVERFLOW
        uint128 current_price = s_starting_price + s_price_delta * uint128((now - s_starting_time) / s_time_delta);
        if (current_price > s_limit_price) {
            current_price = s_limit_price;
        } 
        return (b <= current_price);
    }
}