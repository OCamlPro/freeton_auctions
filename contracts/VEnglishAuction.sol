pragma ton-solidity >=0.44;

import "Constants.sol";
import "IEnglishAuction.sol";

abstract contract VEnglishAuction is Constants, IEnglishAuction {
    
    address static s_owner; // The auction owner
    uint256 static s_auction_start; // The start of the auction
    uint128 static s_starting_price; // The auction starting price
    uint256 static s_max_tick; // After s_max_tick time without any new message, aution ends
    uint256 static s_max_time; // After s_max_time from the auction start, auction ends
    uint256 static s_id; // Unique ID of the auction

    optional(Bidder) best_bidder; // The best bidder
    
    uint256 last_bid; // The last bid timestamp

    constructor() public {
        tvm.accept ();
        // TODO: check static variables consistency
    }

    // This function will test if a given bid can replace the current one.
    // The bid is the amount of tons sent to the contract.
    // Forward: the new bid must be strictly higher than the current one.
    // Reverse: the new bid must be strictly lower than the current one.
    //
    // NB: note that you can encode any rule for this function (for example, 
    // checking that a new bid is higher than the current bid + a given limit)
    // but the whole logic of the English Auction is described here.
    function newBidIsBetterThan(uint128 old_bid) virtual internal returns (bool);

    // Sets the bidder of the storage.
    // For obvious reasons, this function must not be external/public.
    function setBidder() internal{
        best_bidder.set(Bidder(msg.sender, msg.value));
    }

    // Checks if the auction is over.
    // It can either have reached the time limit of the auction or have 
    // no transaction after some time.  
    function auctionOver() internal view returns (bool) {
        return (
            now - last_bid >= s_max_tick || 
            now - s_auction_start >= s_max_time);
    }

    // Sends a bid.
    // If it is incorrect, refunds the bidder.
    function bid() external override {
        tvm.accept();
        require (!auctionOver(), E_AUCTION_OVER);
        if (best_bidder.hasValue()) {
            Bidder b = best_bidder.get();
            if (newBidIsBetterThan(b.bid)) {
              // New winner
              setBidder();
              // TODO: call bidder refund function
              // currentBestBidder().transfer(b.bid, false, 2, ?)
            } else {
                // No new winner
                // TODO: call callback_refund function
                // msg.sender.transfer(b.bid, false, 2, ?)
            }
        } else {
            if (newBidIsBetterThan(s_starting_price)){
                setBidder();
            } else {
                emit InvalidBid(); 
            }
        }
    }

    // Once the auction has ended, this function emits the winner
    // and destroys itself.
    // TODO: Winner emission from root
    function endAuction() external override {
        tvm.accept();
        if (auctionOver()){
            if (best_bidder.hasValue()) {
              Bidder b = best_bidder.get();
              emit Winner(b.bidder, b.bid);
              // TODO: call callback_winner
            }
            selfdestruct(s_owner);
        } else {
            emit AuctionNotFinished();
        }
    }




}