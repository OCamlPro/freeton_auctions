pragma ton-solidity >=0.44;

import "Constants.sol";
import "DutchAuction.sol";
import "DutchReverseAuction.sol";
import "EnglishAuction.sol";
import "EnglishReverseAuction.sol";
import "IBidBuilder.sol";
import "BidBuilder.sol";
import "IAuctionRoot.sol";

contract AuctionRoot is Constants, IAuctionRoot {

    // address static s_owner; // The owner of the auction root. Superfluous?
    address static s_bid_address_reference; // The address of the reference bid address
    optional(TvmCell) s_english_code; // The English Auction code
    optional(TvmCell) s_english_reverse_code; // The English Reverse Auction code
    optional(TvmCell) s_dutch_code; // The Dutch Auction code
    optional(TvmCell) s_dutch_reverse_code; // The Dutch Reverse Auction code

    optional(TvmCell) s_bid_builder_code; // The BidBuilder code

    uint256 id; // A counter for guvung unique IDs to auctions 

    constructor(address bid_address) public{
        tvm.accept();
        id = 0;
        s_bid_address_reference = bid_address;
    }

    // When initializing codes, checking if they already have been initialized.
    // If so, fails.
    modifier uninitialized(optional(TvmCell) v){
        require (!v.hasValue(), E_ALREADY_INITIALIZED);
        _;
    }

    modifier atLeast(uint128 i){
        require (msg.value >= i, E_VALUE_TOO_LOW);
        _;
    }

    // Sets the English Auction code
    function setEnglishCode(TvmCell code) override external uninitialized(s_english_code){
        tvm.accept();
        s_english_code.set(code);
        emit Ok();
    }

    // Sets the English Reverse Auction code
    function setEnglishReverseCode(TvmCell code) override external uninitialized(s_english_reverse_code){
        tvm.accept();
        s_english_reverse_code.set(code);
        emit Ok();
    }

    // Sets the Dutch Auction code
    function setDutchCode(TvmCell code) override external uninitialized(s_dutch_code){
        tvm.accept();
        s_dutch_code.set(code);
        emit Ok();
    }

    // Sets the Dutch Reverse Auction code
    function setDutchReverseCode(TvmCell code) override external uninitialized(s_dutch_reverse_code){
        tvm.accept();
        s_dutch_reverse_code.set(code);
        emit Ok();
    }

    // Sets the BidBuilder code
    function setBidBuilderCode(TvmCell code) override external uninitialized(s_bid_builder_code){
        tvm.accept();
        s_bid_builder_code.set(code);
        emit Ok();
    }

    // Initializes the different contract variables storing the contract codes.
    function init(
        address english_auction, 
        address english_reverse_auction, 
        address dutch_auction, 
        address dutch_reverse_auction,
        address bid_builder
        ) pure override external{
        tvm.accept();
        IBuildable(english_auction).thisIsMyCode{value:1 ton, callback: this.setEnglishCode}();
        IBuildable(english_reverse_auction).thisIsMyCode{value:1 ton, callback: this.setEnglishReverseCode}();
        IBuildable(dutch_auction).thisIsMyCode{value:1 ton, callback: this.setDutchCode}();
        IBuildable(dutch_reverse_auction).thisIsMyCode{value:1 ton, callback: this.setDutchReverseCode}();
        IBuildable(bid_builder).thisIsMyCode{value:1 ton, callback: this.setBidBuilderCode}();
    }

    // Deploys a Bid Builder.
    // A bid builder requires a root wallet, whose interface is IRootWallet.
    function deployBidBuilder(address root_wallet) internal returns (address){
        IBidBuilder b = new BidBuilder
        {
            value: 0.4 ton,
            code: s_bid_builder_code.get(),
            varInit:{
                s_root_wallet: root_wallet,
                s_auction_id: id
            }
        }();
        return address(b);
    }

    function initBidBuilder(address bid_builder, address auction_address) view override external{
        IBidBuilder(bid_builder).init{value: 1 ton}(
            s_bid_address_reference,
            auction_address
        );
    }

    // Deploys a Dutch Auction and its associated BidBuilder.
    function deployDutchAuction(
        address root_wallet,
        address winner_processor,
        uint256 start_price, 
        uint256 end_price, 
        uint256 price_delta, 
        uint256 time_delta
        ) override external atLeast(1 ton) {
        tvm.accept();
        address bid_builder = deployBidBuilder(root_wallet);
        DutchAuction c = 
          new DutchAuction
            {
            value: 0,
            flag: 128,
            code: s_dutch_code.get(),
            pubkey: msg.pubkey(),
            varInit: 
                {
                    s_owner: msg.sender,
                    s_starting_price: start_price,
                    s_limit_price: end_price,
                    s_price_delta: price_delta,
                    s_time_delta: time_delta,
                    s_id: id,
                    s_bid_builder_address: bid_builder,
                    s_winner_processor_address: winner_processor
                }
            }();
        ++id;
        emit AuctionCreated(address(c));
    }

    // Deploys a Dutch Reverse Auction and its associated BidBuilder.
    function deployDutchReverseAuction(
        address root_wallet,
        address winner_processor,
        uint256 start_price, 
        uint256 end_price, 
        uint256 price_delta, 
        uint256 time_delta) override external atLeast(1 ton) {
        tvm.accept();
        address bid_builder = deployBidBuilder(root_wallet);
        DutchReverseAuction c = 
          new DutchReverseAuction
            {
            value: 0,
            flag: 128,
            code: s_dutch_reverse_code.get(),
            pubkey: msg.pubkey(),
            varInit: 
                {
                    s_owner: msg.sender,
                    s_starting_price: start_price,
                    s_limit_price: end_price,
                    s_price_delta: price_delta,
                    s_time_delta: time_delta,
                    s_id: id,
                    s_bid_builder_address: bid_builder,
                    s_winner_processor_address: winner_processor
                }
            }();
        ++id;
        emit AuctionCreated(address(c));
    }

    // Deploys a English Auction and its associated BidBuilder.
    function deployEnglishAuction(
        address root_wallet,
        address winner_processor,
        uint256 start_price, 
        uint256 max_tick, 
        uint256 max_time) override external atLeast(1 ton) {
        tvm.accept();
        address bid_builder = deployBidBuilder(root_wallet);
        EnglishAuction c = 
          new EnglishAuction
            {
            value: 0,
            flag: 128,
            code: s_english_code.get(),
            pubkey: msg.pubkey(),
            varInit: 
                {
                    s_owner: msg.sender,
                    s_starting_price: start_price,
                    s_max_tick: max_tick,
                    s_max_time: max_time,
                    s_id: id,
                    s_bid_builder_address: bid_builder,
                    s_winner_processor_address: winner_processor
                }
            }();
        ++id;
        emit AuctionCreated(address(c));
    }

    // Deploys a English Reverse Auction and its associated BidBuilder.
    function deployEnglishReverseAuction(
        address root_wallet,
        address winner_processor,
        uint256 start_price, 
        uint256 max_tick, 
        uint256 max_time) override external atLeast(1 ton) {
        tvm.accept();
        address bid_builder = deployBidBuilder(root_wallet);
        EnglishReverseAuction c = 
          new EnglishReverseAuction
            {
            value: 0,
            flag: 128,
            code: s_english_reverse_code.get(),
            pubkey: msg.pubkey(),
            varInit: 
                {
                    s_owner: msg.sender,
                    s_starting_price: start_price,
                    s_max_tick: max_tick,
                    s_max_time: max_time,
                    s_id: id,
                    s_bid_builder_address: bid_builder,
                    s_winner_processor_address: winner_processor
                }
            }();
        ++id;
        emit AuctionCreated(address(c));
    }

}