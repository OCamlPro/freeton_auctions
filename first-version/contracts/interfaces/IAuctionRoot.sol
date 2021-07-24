pragma ton-solidity >=0.44;

interface IAuctionRoot{

    function setEnglishCode(TvmCell code) external;
    function setEnglishReverseCode(TvmCell code) external;
    function setDutchCode(TvmCell code) external;
    function setDutchReverseCode(TvmCell code) external;
    function setBidBuilderCode(TvmCell code) external;
    function setRevBidBuilderCode(TvmCell code) external;
    function init(
        address english_auction, 
        address english_reverse_auction, 
        address dutch_auction, 
        address dutch_reverse_auction, 
        address bid_builder,
        address rev_bid_builder
    ) external pure;

    function initBidBuilder(
        address bid_builder, 
        address auction_address,
        bool blind
    ) external view;

    function initRevBidBuilder(
        address bid_builder, 
        address auction_address,
        bool blind,
        address winner_processor_ref
    ) external view;

    function deployDutchAuction(
        address root_wallet,
        address winner_processor,
        uint256 start_price, 
        uint256 end_price, 
        uint256 price_delta, 
        uint256 time_delta
    ) external;

    function deployDutchReverseAuction(
        address root_wallet,
        address winner_processor,
        uint256 start_price, 
        uint256 end_price, 
        uint256 price_delta, 
        uint256 time_delta
    ) external;

    function deployEnglishAuction(
        address root_wallet,
        address winner_processor,
        uint256 start_price, 
        uint256 max_tick, 
        uint256 max_time
    ) external ;

    function deployEnglishReverseAuction(
        address root_wallet,
        address winner_processor,
        uint256 start_price, 
        uint256 max_tick, 
        uint256 max_time
    ) external ;
}