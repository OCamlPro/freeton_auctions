pragma ton-solidity >=0.44;

import "Bid.sol";
import "Constants.sol";
import "Buildable.sol";
import "interfaces/IBidBuilder.sol";

contract BidBuilder is Constants, Buildable, IBidBuilder {

    optional(TvmCell) bid_code; // Code of the bid contract, to be initialized
    optional(address) auction_address; // Auction address, to be initialized

    address static s_root_wallet; // Wallet root
    uint256 static s_auction_id; // Auction id (useful for address uniqueness)
    address static s_winner_processor; // The winner processor
    uint256 id; // Id for the created bids

    modifier uninitializedCell(optional(TvmCell) opt){
        require (!opt.hasValue(), E_ALREADY_INITIALIZED);
        _;
    }

    modifier uninitializedAddr(optional(address) opt){
        require (!opt.hasValue(), E_ALREADY_INITIALIZED);
        _;
    }

    modifier initializedCell(optional(TvmCell) opt){
        require (opt.hasValue(), E_UNINITIALIZED);
        _;
    }

    modifier initializedAddr(optional(address) opt){
        require (opt.hasValue(), E_UNINITIALIZED);
        _;
    }

    function setCode(TvmCell code) uninitializedCell(bid_code) external{
        tvm.accept();
        bid_code.set(code);
        emit Ok();
    }

    function init(address bid_address, address auction_addr)
        override external uninitializedAddr(auction_address){
        tvm.accept();
        auction_address.set(auction_addr);
        IBuildable(bid_address).thisIsMyCode{value:0 ton, flag: 128, callback:this.setCode}();
    }

    constructor() public{
        tvm.accept();
        id = 0;
        emit Ok();
    }

    // For Forward auctions, commitment = amount
    // For Reverse auctions, commitment = address
    // For Blind auctions, commitment = hash(salt, amount / address) (check Hasher.sol)
    function deployBid(uint256 commitment) override external 
        initializedAddr(auction_address)
        initializedCell(bid_code) {
        tvm.accept();
        // TODO: reserve funds instead of 0.5 ton
        Bid b =
            new Bid
            {
                value:0.5 ton,
                code: bid_code.get(),
                varInit: 
                {
                    s_auction: auction_address.get(),
                    s_bid_builder: address(this),
                    s_bidder: msg.sender,
                    s_commitment: commitment,
                    s_id: id,
                    s_root_wallet: s_root_wallet
                }
            }();
        ++id;
        emit ThisIsYourBid(auction_address.get(), id, address(b), s_root_wallet);
    }

    // Validates the correctness of a bid to an auction. 
    // It can only be called by a bid the current bid builder has created. 
    function validateBid(
        address bidder, 
        address vault_address, 
        uint256 commitment, 
        uint256 bid_id
    ) external view override {
        // 1. Checking the bid has been built by the current bid builder
        tvm.accept();

        TvmCell stateInit = 
            tvm.buildStateInit({
                code: bid_code.get(),
                pubkey: msg.pubkey(),
                contr: Bid,
                varInit:{
                    s_auction: auction_address.get(),
                    s_bid_builder: address(this),
                    s_bidder: bidder,
                    s_commitment: commitment,
                    s_id: bid_id,
                    s_root_wallet: s_root_wallet
                }
            });

        require (msg.sender == address(tvm.hash(stateInit)), E_UNAUTHORIZED);

        // 2. Validating the bid
        Bidder b = Bidder(bidder, commitment, msg.sender, vault_address, s_winner_processor); 
        IAuction(auction_address.get()).
            validateBid {
                value: 0,
                flag: 128
            }(b);
    }

}