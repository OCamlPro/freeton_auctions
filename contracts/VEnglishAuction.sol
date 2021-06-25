pragma ton-solidity >=0.44;

import "Constants.sol";
import "IEnglishAuction.sol";

abstract contract VEnglishAuction is Constants, IEnglishAuction {
    
    address static s_owner; // The auction owner
    uint256 s_auction_start; // The start of the auction
    uint128 static s_starting_price; // The auction starting price
    uint256 static s_max_tick; // After s_max_tick time without any new message, aution ends
    uint256 static s_max_time; // After s_max_time from the auction start, auction ends

    optional(Bidder) best_bidder; // The best bidder
    
    uint256 last_bid; // The last bid timestamp

    constructor() public {
        tvm.accept ();
        // TODO: check static variables consistency
    }

    function newBidIsBetterThan(uint128 old_bid) virtual internal returns (bool);

    function setBidder(uint32 callback_refund, uint32 callback_winner) internal{
        best_bidder.set(Bidder(msg.sender, callback_refund, callback_winner, msg.value));
    }

    function bid(uint32 callback_refund, uint32 callback_winner) external override {
        tvm.accept();
        if (best_bidder.hasValue()) {
            Bidder b = best_bidder.get();
            if (newBidIsBetterThan(b.bid)) {
              // New winner
              setBidder(callback_refund, callback_winner);
              // TODO: call bidder refund function
              // currentBestBidder().transfer(b.bid, false, 2, ?)
            } else {
                // No new winner
                // TODO: call callback_refund function
                // msg.sender.transfer(b.bid, false, 2, ?)
            }
        } else {
            if (newBidIsBetterThan(s_starting_price)){
                setBidder(callback_refund, callback_winner);
            } else {
               emit InvalidBid(); 
            }
        }
    }

    function endAuction() external override {
        tvm.accept();
        if (now - last_bid >= s_max_tick || now - s_auction_start >= s_max_time){
            // TODO: call callback_winner
            selfdestruct(s_owner);
        } else {
            emit AuctionNotFinished();
        }
    }




}