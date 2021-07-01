pragma ton-solidity >=0.44;

import "Constants.sol";
import "IDutchAuction.sol";
import "IAuction.sol";

// The main contract for the Dutch and Reverse Dutch Auction
// https://en.wikipedia.org/wiki/Dutch_auction

abstract contract VDutchAuction is Constants, IDutchAuction {
    address static s_owner; // The owner of the auction
    uint128 static s_starting_price; // The starting price
    uint256 static s_starting_time; // The starting time
    uint128 static s_limit_price; // The limit price
    uint128 static s_price_delta; // The price decrement over time
    uint256 static s_time_delta; // The time after which the time
    uint256 static s_id;

    address static s_processor; // The Winner processor

    constructor() public{
        tvm.accept();
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
    // TODO: emission of Winner in Root.
    function betterPriceThanCurrent(uint128) internal virtual returns(bool);

    // A (correct) bid automatically ends the auction.
    function receiveBid(uint128 commitment) external override fromBidBuilder {
        tvm.accept ();
        if (betterPriceThanCurrent(commitment)){
            emit Winner (msg.sender, commitment);
            IProcessWinner(s_processor).acknowledgeWinner{/* TODO */}(msg.sender, commitment);
        } else {
            emit InvalidBid();
            // Todo: cleaner fail
            IBid(msg.sender).transferToOwner{/* TODO */}();
        }
    }

    function bid(uint128 amount) {
        BidBuilder(s_bid_builder_address).deployBid{value: 1 ton}(address(this), amount);
    }
    
    // If no bid has been done and the limit price is the best price,
    // the auction can be terminated.
    // TODO: emission of NoWinner in Root.
    function endAuction() external override {
        if (betterPriceThanCurrent(s_limit_price)) {
            emit NoWinner();
            selfdestruct(s_owner);
        }
    }

    function thisIsMyCode() external override responsible returns(TvmCell) {
        tvm.accept();
        return {value: 1 ton} tvm.code();
    }
}