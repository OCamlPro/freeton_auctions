pragma ton-solidity >=0.44;

import "interfaces/IVault.sol";
import "interfaces/IAuction.sol";
import "interfaces/IRootWallet.sol";
import "interfaces/IReverseBidBuilder.sol";
import "Constants.sol";
import "Buildable.sol";

contract ReverseBid is Constants, Buildable {

    // The auction associated to this bid    
    address static s_auction;

    // The builder of this bid    
    address static s_bid_builder;

    // The bidder
    address static s_bidder;

    // Commitment
    // For non blind auctions, commitment = amount
    // For blind auctions, commitment = hash(salt, amount)
    uint256 static s_commitment;

    // Unique Bid ID
    uint256 static s_id;

    // Root wallet
    address static s_root_wallet;

    // The vault address.
    address static s_vault_address;

    // The winner processor address
    address static s_winner_processor;

    // TODO: take into account everything may fail for an unknown reason :
    // After the end of the auction, send back any unused fund?

    constructor() public{
        tvm.accept();
    }

    // Starts the check vault process
    // Will request the wallet address
    // Can be started by anyone
    function checkWinnerProcessor() external view {
        IReverseBidBuilder(s_bid_builder).
            validateBid {
                value: 0.4 ton
            }(s_bidder, s_vault_address, s_commitment, s_id, s_winner_processor);
    }

}