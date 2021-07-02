pragma ton-solidity >=0.44;

import "IVault.sol";
import "IAuction.sol";
import "Constants.sol";
import "IRootWallet.sol";
import "Buildable.sol";

contract Bid is Constants, Buildable {

    // The auction associated to this bid    
    address static s_auction;

    // The bidder
    address static s_bidder;

    // Commitment
    // For English/Dutch auctions, commitment = amount
    uint256 static s_commitment;

    // Unique Bid ID
    uint256 static s_id;

    // Root wallet
    address static s_root_wallet;

    // The wallet address.
    optional(address) wallet_address;

    // TODO: take into account everything may fail for an unknown reason :
    // After the end of the auction, send back any unused fund?

    constructor() public{
        tvm.accept();
        emit BidPubkey(s_auction, s_id, tvm.pubkey());
    }

    modifier onlyFrom(address a){
        require(msg.sender == a, E_UNAUTHORIZED);
        _;
    }

    // Starts the check vault process
    // Will request the wallet address
    // Can be started by anyone
    function checkVault() external view {
        IRootWallet(s_root_wallet).getWalletAddress
        {
            value:1 ton,
            callback:this.checkVaultAddr
        }(0,tvm.pubkey());
    }

    // Requests the balance of the vault address
    function checkVaultAddr(address a) external onlyFrom(s_root_wallet){
        wallet_address.set(a);
        IVault(a).getBalance{
            value: 1 ton,
            callback: this.checkVaultContent
        }();
    }

    // Checks the amount in the wallet is bigger than the commitment
    function checkVaultContent(uint256 amount) external view onlyFrom(wallet_address.get()){
        // Warning: modifier may fail if wallet_address not set by checkVaultAddr
        require(amount >= s_commitment, E_INVALID_BID);
        uint128 grams = 10000;
        IVault(wallet_address.get()).
            transfer{value: 1 ton}(s_bidder, amount - s_commitment, grams);
        IAuction(s_auction).validateBid{value: 1 ton}(s_bidder, s_commitment);
    }

    function transferVaultContent(address dest) public view onlyFrom(s_auction){
        uint128 grams = 10000;
        IVault(wallet_address.get()).transfer(dest, s_commitment, grams);
    }

    function transferVaultContentToOwner() external view onlyFrom(s_auction){
        transferVaultContent(s_bidder);
    }

}