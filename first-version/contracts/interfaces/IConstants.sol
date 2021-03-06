pragma ton-solidity >=0.44;

interface IConstants{

    struct Bidder{
        address bidder; // The bidder
        uint256 bid;
        address bid_contract;
        address bid_vault;
        address bid_process_winner;
    }

    event Winner(address, uint256);
    event NoWinner();
    event Loser(address, uint256);
    event InvalidBid();
    event AuctionNotFinished();
    event BidCreated(address);
    event AuctionCreated(address auction, address bid_builder);
    event BidPubkey(address auction, uint256 bid_id, uint256 bid_pubkey);
    event ThisIsYourBid(address auction, uint256 bid_id, address bid, address root_wallet);
    event Ok();
    event RevelationSuccess();

}