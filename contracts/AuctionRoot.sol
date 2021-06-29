pragma ton-solidity >=0.44;

import "Constants.sol";
import "DutchAuction.sol";
import "DutchReverseAuction.sol";
import "EnglishAuction.sol";
import "EnglishReverseAuction.sol";

contract AuctionRoot is Constants{

    address static s_owner;
    optional(TvmCell) s_english_code;
    optional(TvmCell) s_english_reverse_code;
    optional(TvmCell) s_dutch_code;
    optional(TvmCell) s_dutch_reverse_code;

    uint256 id;

    int32 constant ID_SET_ENGLISH_CODE = 201;
    int32 constant ID_SET_ENGLISH_REVERSE_CODE = 202;
    int32 constant ID_SET_DUTCH_CODE = 203;
    int32 constant ID_SET_DUTCH_REVERSE_CODE = 204;

    constructor() public{
        tvm.accept();
        id = 0;
    }

    modifier uninitialized(optional(TvmCell) v){
        require (!v.hasValue(), E_ALREADY_INITIALIZED);
        _;
    }

    function setEnglishCode(TvmCell e) external uninitialized(s_english_code){
        tvm.accept();
        s_english_code = e;
        emit Ok();
    }

    function setEnglishReverseCode(TvmCell e) external uninitialized(s_english_reverse_code){
        tvm.accept();
        s_english_reverse_code = e;
        emit Ok();
    }

    function setDutchCode(TvmCell e) external uninitialized(s_dutch_code){
        tvm.accept();
        s_dutch_code = e;
        emit Ok();
    }

    function setDutchReverseCode(TvmCell e) external uninitialized(s_dutch_reverse_code){
        tvm.accept();
        s_dutch_reverse_code = e;
        emit Ok();
    }

    function init(address ec, address erc, address dc, address drc) pure external{
        tvm.accept();
        EnglishAuction(ec).thisIsMyCode{value:1 ton, callback: this.setEnglishCode}();
        EnglishReverseAuction(erc).thisIsMyCode{value:1 ton, callback: this.setEnglishReverseCode}();
        DutchAuction(dc).thisIsMyCode{value:1 ton, callback: this.setDutchCode}();
        DutchReverseAuction(drc).thisIsMyCode{value:1 ton, callback: this.setDutchReverseCode}();
    }

    function deployDutchAuction(uint128 start_price, uint128 end_price, uint128 price_delta, uint256 time_delta) external{
        DutchAuction c = 
          new DutchAuction
            {
            value: 5 ton,
            code: s_dutch_code.get(),
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
            value: 5 ton,
            code: s_dutch_reverse_code.get(),
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
            value: 5 ton,
            code: s_english_code.get(),
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
            value: 5 ton,
            code: s_english_reverse_code.get(),
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