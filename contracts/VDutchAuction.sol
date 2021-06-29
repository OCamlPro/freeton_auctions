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
    function bid() external override {
        tvm.accept ();
        if (betterPriceThanCurrent(msg.value)){
            emit Winner (msg.sender, msg.value);
            // TODO: call winner_callback function
            selfdestruct(s_owner);
        } else {
            emit InvalidBid();
        }
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