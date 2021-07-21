pragma ton-solidity >=0.44;

import "Constants.sol";
import "interfaces/IAuction.sol";
import "interfaces/IProcessWinner.sol";
import "Buildable.sol";
import "interfaces/IBidBuilder.sol";
import "interfaces/IBid.sol";

abstract contract VEnglishAuction is Constants, IAuction, Buildable {
    
    address static s_owner; // The auction owner
    uint256 static s_auction_start; // The start of the auction
    uint256 static s_starting_price; // The auction starting price
    uint256 static s_max_tick; // After s_max_tick time without any new message, aution ends
    uint256 static s_max_time; // After s_max_time from the auction start, auction ends
    uint256 static s_id; // Unique ID of the auction
    address static s_bid_builder_address; // The address of the bid builder
    address static s_winner_processor_address; // The Winner processor

    optional(Bidder) best_bidder;
    uint256 last_bid_timestamp;

    constructor() public {
        tvm.accept ();
        s_auction_start = now;
        last_bid_timestamp = now;
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
    function newBidIsBetterThan(uint256 old_bid, uint256 new_bid) virtual internal returns (bool);

    // Checks if the auction is over.
    // It can either have reached the time limit of the auction or have 
    // no transaction after some time.
    function auctionOver() internal view returns (bool) {
        return (
            (
                now - last_bid_timestamp >= s_max_tick && 
                best_bidder.hasValue()
            ) ||
            now - s_auction_start >= s_max_time);
    }

    function validateBid ( Bidder new_bidder ) external override onlyFrom(s_bid_builder_address) {
        tvm.accept();
        require (!auctionOver(), E_AUCTION_OVER);
        uint256 current_price;
        bool already_has_a_bidder = best_bidder.hasValue();

        if (already_has_a_bidder) {
            current_price = best_bidder.get().bid;
        } else {
            current_price = s_starting_price;
        }

        if (newBidIsBetterThan(current_price, new_bidder.bid)) {
            if (already_has_a_bidder){
                Bidder old = best_bidder.get();
                IBid(old.bid_contract).
                    transferVaultContent{value:0, flag: 128}(old.bidder);
            }
            best_bidder.set(new_bidder);

        } else {
            emit InvalidBid();
            require(false, E_INVALID_BID); 
            // TODO: refund bidder
        }
    }

    // Starts the bid process
    function bid(uint256 commitment) external override {
        tvm.accept();
        require (!auctionOver(), E_AUCTION_OVER);
        uint256 current_price;
 
        if (best_bidder.hasValue()) {
            current_price = best_bidder.get().bid;
        } else {
            current_price = s_starting_price;
        }

        if (newBidIsBetterThan(current_price, commitment)) {    
            IBidBuilder(s_bid_builder_address).
                deployBid{value:0, flag: 128}(commitment);
        } else {
            emit InvalidBid();
            require(false, E_INVALID_BID);
            // TODO: refund bidder
        }
    }

    // Ends an auction if the bidding time has passed.
    function endAuction() external override {
        tvm.accept();
        if (auctionOver()){
            if (best_bidder.hasValue()) {
                Bidder b = best_bidder.get();
                emit Winner(b.bidder, b.bid);
                // TODO: check value parameters
                IBid(b.bid_contract).
                    transferVaultContent{value:0.1 ton}(s_owner);
                IProcessWinner(s_winner_processor_address).
                    acknowledgeWinner{value:0.2 ton}(b);
            } else {
                IProcessWinner(s_winner_processor_address).
                    acknowledgeNoWinner{value:0, flag: 128}();
            }
            selfdestruct(s_owner);
        } else {
            emit AuctionNotFinished();
            require(false, E_AUCTION_NOT_OVER);
        }
    }
}