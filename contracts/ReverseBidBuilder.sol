pragma ton-solidity >=0.44;

import "Bid.sol";
import "Constants.sol";
import "Buildable.sol";
import "interfaces/IReverseBidBuilder.sol";
import "ReverseBid.sol";

contract ReverseBidBuilder is Constants, Buildable, IReverseBidBuilder {

    optional(TvmCell) bid_code; // Code of the bid contract, to be initialized
    optional(TvmCell) winner_process_code; // Code of the sold contract
    optional(address) auction_address; // Auction address, to be initialized

    address static s_root_wallet; // Wallet root
    uint256 static s_auction_id; // Auction id (useful for address uniqueness)
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

    function setWPCode(TvmCell code) uninitializedCell(winner_process_code) external{
        tvm.accept();
        winner_process_code.set(code);
        emit Ok();
    }

    function init(address bid_address, address auction_addr, address process_winner_ref)
        override external uninitializedAddr(auction_address){
        tvm.accept();
        auction_address.set(auction_addr);
        IBuildable(bid_address).thisIsMyCode{value:1 ton, callback:this.setCode}();
        IBuildable(process_winner_ref).thisIsMyCode{value:1 ton, callback:this.setWPCode}();
    }

    constructor() public{
        tvm.accept();
        id = 0;
        emit Ok();
    }

    // For Forward auctions, commitment = amount
    // For Reverse auctions, commitment = address
    // For Blind auctions, commitment = hash(salt, amount / address) (check Hasher.sol)
    function deployBid(uint256 commitment, address winner_processor) override external 
        initializedAddr(auction_address)
        initializedCell(bid_code) {
        tvm.accept();
        // TODO: reserve funds instead of 0.5 ton
        ReverseBid b =
            new ReverseBid
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
                    s_root_wallet: s_root_wallet,
                    s_winner_processor: winner_processor
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
        uint256 bid_id,
        address winner_processor
    ) external view override {
        // 1. Checking the bid has been built by the current bid builder
        tvm.accept();

        TvmCell stateInit = 
            tvm.buildStateInit({
                code: bid_code.get(),
                pubkey: msg.pubkey(),
                contr: ReverseBid,
                varInit:{
                    s_auction: auction_address.get(),
                    s_bid_builder: address(this),
                    s_bidder: bidder,
                    s_commitment: commitment,
                    s_id: bid_id,
                    s_root_wallet: s_root_wallet,
                    s_winner_processor: winner_processor
                }
            });

        require (msg.sender == address(tvm.hash(stateInit)), E_UNAUTHORIZED);

        // 2. Validating the bid
        Bidder b = Bidder(bidder, commitment, msg.sender, vault_address, winner_processor); 
        IAuction(auction_address.get()).
            validateBid {
                value: 0,
                flag: 128
            }(b);
    }

}