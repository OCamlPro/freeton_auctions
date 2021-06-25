pragma ton-solidity >=0.44;

import "Constants.sol";
import "IDutchAuction.sol";

abstract contract VDutchAuction is Constants, IDutchAuction {
    address s_owner;
    uint128 s_starting_price; // The starting price
    uint256 s_starting_time; // The starting time
    uint128 s_limit_price; // The limit price
    uint128 s_price_delta; // The price decrement over time
    uint256 s_time_delta; // The time after which the time 

    constructor() public{
        tvm.accept();
    }

    function betterPriceThanCurrent(uint128) internal virtual returns(bool);

    function buy() external override {
        tvm.accept ();
        if (betterPriceThanCurrent(msg.value)){
            selfdestruct(s_owner);
        } else {
            emit InvalidBid();
        }
    }
    
    function endAuction() external override {
        require(msg.sender == s_owner, E_UNAUTHORIZED);
        if (betterPriceThanCurrent(s_limit_price)) {
            selfdestruct(s_owner);
        }
    }
}