pragma ton-solidity >=0.44;

import "Constants.sol";
import "DutchAuction.sol";
import "DutchReverseAuction.sol";
import "EnglishAuction.sol";
import "EnglishReverseAuction.sol";

contract AuctionRoot is Constants{

    address static s_owner;
    TvmCell static s_english_code;
    TvmCell static s_english_reverse_code;
    TvmCell static s_dutch_code;
    TvmCell static s_dutch_reverse_code;

    uint256 id;

    constructor() public{
        tvm.accept();
    }

    function deployDutchAuction(uint128 start_price, uint128 end_price, uint128 price_delta, uint256 time_delta) external{
        DutchAuction c = 
          new DutchAuction
            {
            value: msg.value - 10,
            code: s_dutch_code,
            pubkey: msg.pubkey(),
            varInit: 
                {
                    s_owner: msg.sender,
                    s_starting_price: start_price,
                    s_starting_time: now,
                    s_limit_price: end_price,
                    s_price_delta: price_delta,
                    s_time_delta: time_delta,
                    s_id: id
                }
            }();
        ++id;
        emit AuctionCreated(address(c));
    }

    function deployReverseDutchAuction(uint128 start_price, uint128 end_price, uint128 price_delta, uint256 time_delta) external{
        DutchReverseAuction c = 
          new DutchReverseAuction
            {
            value: msg.value - 10,
            code: s_dutch_reverse_code,
            pubkey: msg.pubkey(),
            varInit: 
                {
                    s_owner: msg.sender,
                    s_starting_price: start_price,
                    s_starting_time: now,
                    s_limit_price: end_price,
                    s_price_delta: price_delta,
                    s_time_delta: time_delta,
                    s_id: id
                }
            }();
        ++id;
        emit AuctionCreated(address(c));
    }

    function deployEnglishAuction(uint128 start_price, uint256 max_tick, uint256 max_time) external{
        EnglishAuction c = 
          new EnglishAuction
            {
            value: msg.value - 10,
            code: s_english_code,
            pubkey: msg.pubkey(),
            varInit: 
                {
                    s_owner: msg.sender,
                    s_auction_start: now,
                    s_starting_price: start_price,
                    s_max_tick: max_tick,
                    s_max_time: max_time,
                    s_id: id
                }
            }();
        ++id;
        emit AuctionCreated(address(c));
    }

    function deployReverseEnglishAuction(uint128 start_price, uint256 max_tick, uint256 max_time) external {
        EnglishReverseAuction c = 
          new EnglishReverseAuction
            {
            value: msg.value - 10,
            code: s_english_reverse_code,
            pubkey: msg.pubkey(),
            varInit: 
                {
                    s_owner: msg.sender,
                    s_auction_start: now,
                    s_starting_price: start_price,
                    s_max_tick: max_tick,
                    s_max_time: max_time,
                    s_id: id
                }
            }();
        ++id;
        emit AuctionCreated(address(c));
    }

}