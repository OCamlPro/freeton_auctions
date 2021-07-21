pragma ton-solidity >=0.44;

import "Constants.sol";
import "interfaces/IAuction.sol";
import "interfaces/IProcessWinner.sol";
import "Buildable.sol";
import "interfaces/IBidBuilder.sol";
import "interfaces/IBid.sol";

// The main contract for the Dutch and Reverse Dutch Auction
// https://en.wikipedia.org/wiki/Dutch_auction

abstract contract VDutchAuction is Constants, Buildable, IAuction {
    address static s_owner; // The owner of the auction
    uint256 static s_starting_price; // The starting price
    uint256 static s_auction_start; // The starting time
    uint256 static s_limit_price; // The limit price
    uint256 static s_price_delta; // The price decrement over time
    uint256 static s_time_delta; // The time after which the time
    uint256 static s_id; // Unique ID of the auction
    address static s_bid_builder_address; // The address of the bid builder
    address static s_winner_processor_address; // The Winner processor

    constructor() public{
        tvm.accept();
        s_auction_start = now;
    }

    // This funcion will calculate the current price given the starting price
    // and its evolution through time.
    // * Forward : the current price starts with s_starting_price and is 
    //   decremented of s_price_delta after s_time_delta. 
    //   Its minimum is s_limit_price.
    //   Returns true if the value in argument is higher or equal to the 
    //   current price.
    //
    // * Backward : the current price starts with s_starting_price and is 
    //   incremented of s_price_delta after s_time_delta. 
    //   Its maximum is s_limit_price.
    //   Returns true if the value in argument is higher or equal to the 
    //   current price.
    function betterPriceThanCurrent(uint256) internal virtual returns(bool);

    // Validates a bid.
    // In the Dutch version, a valid bid automatically ends the auction
    function validateBid(Bidder auction_winner) external override onlyFrom(s_bid_builder_address) {
        tvm.accept ();
        if (betterPriceThanCurrent(auction_winner.bid)){
            IProcessWinner(s_winner_processor_address).
                acknowledgeWinner{value:0.2 ton}(auction_winner);
            IBid(auction_winner.bid_contract).transferVaultContent{value:0.2 ton}(s_owner);
        } else {
            emit InvalidBid();
        }
    }

    // Starts the bid process
    function bid(uint256 commitment) external override {
        tvm.accept();
        if (betterPriceThanCurrent(commitment)){
          IBidBuilder(s_bid_builder_address).
            deployBid{value: 0, flag: 128}(commitment);
        } else {
            emit InvalidBid();
        }
    }
    
    // Ends an auction.
    // If no bid has been done and the limit price is the best price,
    // the auction can be terminated.
    function endAuction() external override {
        tvm.accept();
        if (betterPriceThanCurrent(s_limit_price)) {
            emit NoWinner();
            IProcessWinner(s_winner_processor_address).acknowledgeNoWinner{value:0, flag: 128}();
            selfdestruct(s_owner);
        }
    }
}