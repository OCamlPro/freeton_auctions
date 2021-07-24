pragma ton-solidity >=0.44;

import "interfaces/IVault.sol";
import "interfaces/IAuction.sol";
import "interfaces/IRootWallet.sol";
import "interfaces/IBidBuilder.sol";
import "Constants.sol";
import "Buildable.sol";

contract Bid is Constants, Buildable {

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

    // Winner processor
    address static s_winner_processor;

    // The vault address.
    optional(address) vault_address;

    // TODO: take into account everything may fail for an unknown reason :
    // After the end of the auction, send back any unused fund?

    constructor() public{
        tvm.accept();
    }

    // Starts the check vault process
    // Will request the wallet address
    // Can be started by anyone
    function checkVault() external view {
        IRootWallet(s_root_wallet).getWalletAddress {
            value: 0.8 ton,
            callback:this.checkVaultAddr
        }(0,tvm.pubkey());
    }

    // Requests the balance of the vault address
    function checkVaultAddr(address a) external onlyFrom(s_root_wallet){
        vault_address.set(a);
        IVault(a).getBalance {
            value: 0.6 ton,
            callback: this.checkVaultContent
        }();
    }

    // Checks the amount in the wallet is bigger than the commitment
    function checkVaultContent(uint256 amount) external view onlyFrom(vault_address.get()){
        // Warning: modifier may fail if wallet_address not set by checkVaultAddr
        require(amount >= s_commitment, E_INVALID_BID);
        
       /* uint128 grams = 10000;
         IVault(vault_address.get()).
            transfer{value: 1 ton}(s_bidder, amount - s_commitment, grams);*/
        IBidBuilder(s_bid_builder).
            validateBid {
                value: 0.4 ton
            }(s_bidder, vault_address.get(), s_commitment, s_id);
    }

    // Transfers the content of the vault.
    // It can go to the auctioneer if this bid correspond to the winning bid, 
    // otherwise it goes to the bidder.
    function transferVaultContent(address dest, uint256 amount) public view onlyFrom(s_auction){
        uint128 grams = 10000;
        if (amount == 0) {
            IVault(vault_address.get()).transfer(dest, s_commitment, grams);
        } else {
            IVault(vault_address.get()).transfer(dest, amount, grams);
        }
    }
}