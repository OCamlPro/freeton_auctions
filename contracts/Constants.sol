pragma ton-solidity >=0.44;

interface IConstants{

    struct Bidder{
        address bidder; // The bidder
        uint256 bid;
        address bid_contract;
        address bid_vault;
    }

    event Winner(address, uint256);
    event NoWinner();
    event Loser(address, uint256);
    event InvalidBid();
    event AuctionNotFinished();
    event BidCreated(address);
    event AuctionCreated(address);
    event BidPubkey(address auction, uint256 bid_id, uint256 bid_pubkey);
    event ThisIsYourBid(address auction, uint256 bid_id, address bid);
    event Ok();

}

contract Constants is IConstants {
    

    uint16 constant E_UNAUTHORIZED = 101;
    uint16 constant E_AUCTION_OVER = 102;
    uint16 constant E_UNINITIALIZED_PUBKEY = 103;
    uint16 constant E_BAD_PUBKEY = 104;
    uint16 constant E_ALREADY_INITIALIZED = 105;
    uint16 constant E_INVALID_BID = 106;
    uint16 constant E_AUCTION_NOT_OVER = 107;
    uint16 constant E_VALUE_TOO_LOW = 108;
    uint16 constant E_UNINITIALIZED = 109;
}