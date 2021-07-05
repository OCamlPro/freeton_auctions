pragma ton-solidity >=0.44;

import "Constants.sol";
import "IDutchAuction.sol";
import "IAuction.sol";
import "IProcessWinner.sol";
import "Buildable.sol";
import "IBidBuilder.sol";

// The main contract for the Dutch and Reverse Dutch Auction
// https://en.wikipedia.org/wiki/Dutch_auction

abstract contract VDutchAuction is Constants, Buildable, IDutchAuction {
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


    modifier onlyFrom(address a){
        require(msg.sender == a, E_UNAUTHORIZED);
        _;
    }

    // A (correct) bid automatically ends the auction.
    function validateBid(address winner, address winner_vault, uint256 commitment) external override {
        // TODO: only from a Bid contract !
        tvm.accept ();
        Bidder auction_winner =
            Bidder(winner, commitment, msg.sender, winner_vault);
        IProcessWinner(s_winner_processor_address).
            acknowledgeWinner{value:0, flag: 128}(auction_winner);
    }

    function bid(uint256 commitment) external override {
        tvm.accept();
        if (betterPriceThanCurrent(commitment)){
          IBidBuilder(s_bid_builder_address).
            deployBid{value: 0, flag: 128}(address(this), commitment);
        } else {
            emit InvalidBid();
        }
    }
    
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