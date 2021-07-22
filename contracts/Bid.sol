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
    // For English/Dutch auctions, commitment = amount
    uint256 static s_commitment;

    // Unique Bid ID
    uint256 static s_id;

    // Root wallet
    address static s_root_wallet;

    // The vault address.
    optional(address) vault_address;

    // TODO: take into account everything may fail for an unknown reason :
    // After the end of the auction, send back any unused fund?

    constructor() public{
        tvm.accept();
        emit BidPubkey(s_auction, s_id, tvm.pubkey());
    }

    // Starts the check vault process
    // Will request the wallet address
    // Can be started by anyone
    function checkVault() external view {
        IRootWallet(s_root_wallet).getWalletAddress {
            value: 0,
            flag: 128,
            callback:this.checkVaultAddr
        }(0,tvm.pubkey());
    }

    // Requests the balance of the vault address
    function checkVaultAddr(address a) external onlyFrom(s_root_wallet){
        vault_address.set(a);
        IVault(a).getBalance {
            value: 0,
            flag: 128,
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
                value: 0,
                flag: 128
            }(s_bidder, vault_address.get(), s_commitment, s_id);
    }

    function transferVaultContent(address dest) public view onlyFrom(s_auction){
        uint128 grams = 10000;
        IVault(vault_address.get()).transfer(dest, s_commitment, grams);
    }
}