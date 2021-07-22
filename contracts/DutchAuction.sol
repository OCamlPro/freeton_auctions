pragma ton-solidity >=0.44;

import "VDutchAuction.sol";
import "Constants.sol";
import "interfaces/IAuction.sol";

contract DutchAuction is Constants, IAuction, VDutchAuction {
    function betterPriceThanCurrent(uint256 b) internal override returns (bool){

        // This should not overflow as:
        // s_time_delta > 0
        // (now-s_auction_start) should be small
        // It COULD overflow if s_price_delta was close to MAX_INT
        uint256 decrement = ((now - s_auction_start) / s_time_delta) * s_price_delta;

        // The current price is max(s_limit_price, s_starting_price - decrement).
        // Checking underflow
        if (decrement > s_starting_price){
            // The decrement is higher than the starting price
            return (b >= s_limit_price);
        }

        uint256 current_price = s_starting_price - decrement;

        if (current_price < s_limit_price) {
            current_price = s_limit_price;
        }

        return (b >= current_price);
    }

    function processWinner(Bidder b) internal override {
        IProcessWinner(b.bid_process_winner).
            acknowledgeWinner{value:0.2 ton}(b);
        IBid(b.bid_contract).transferVaultContent{value:0.2 ton}(s_owner, b.bid);
    }
}