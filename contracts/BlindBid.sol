pragma ton-solidity >=0.44;

import "interfaces/IVault.sol";
import "interfaces/IAuction.sol";
import "interfaces/IRootWallet.sol";
import "interfaces/IBidBuilder.sol";
import "Constants.sol";
import "Buildable.sol";

contract BlindBid is Constants, Buildable {

    // The auction associated to this bid    
    address static s_auction;

    // The builder of this bid    
    address static s_bid_builder;

    // The bidder
    address static s_bidder;

    // Commitment
    // For Blind auctions, commitment = hash (salt, amount) 
    uint256 static s_commitment;

    // Unique Bid ID
    uint256 static s_id;

    // Root wallet
    address static s_root_wallet;

    // The vault address.
    optional(address) m_vault_address;

    // The revealed amount
    optional(uint256) m_amount;

    constructor() public{
        tvm.accept();
    }

    // Returns true if the first value is a better bid than the second.
    function betterBid(uint256, uint256) abstract pure;

    function reveal(uint256 salt, uint256 amount) external onlyFrom(s_bidder){
        bytes b = abi.encodePacked(salt).append(abi.encodePacked(amount));
        require (tvm.hash(b) == s_commitment, E_FAILED_REVELATION);
        s_amount.set(amount);
    }

    function getBid(uint32 pos) external view responsible returns(address){
        if (pos == 0) {
            return address(this);
        }
        else {
            require(m_next_bid.hasValue(), E_NO_NEXT_BID);
            address next = m_next_bid.get();
            if (pos == 1) {
                return next;
                }
            else {
                return BlindBid(next).getBid(pos - 1);
            }
        }
    }

    // Starts the check vault process
    // Will request the wallet address
    // Can be started by anyone
    function checkVault() external view {
        require (s_amount.hasValue(), E_UNINITIALIZED);
        IRootWallet(s_root_wallet).getWalletAddress {
            value: 0,
            flag: 128,
            callback:this.checkVaultAddr
        }(0,tvm.pubkey());
    }

    // Requests the balance of the vault address
    function checkVaultAddr(address a) external onlyFrom(s_root_wallet){
        require (s_amount.hasValue(), E_UNINITIALIZED);
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
        require (s_amount.hasValue(), E_UNINITIALIZED);
        require (amount >= s_amount.get(), E_INVALID_BID);
        IBidBuilder(s_bid_builder).
            validateBid {
                value: 0,
                flag: 128
            }(s_bidder, vault_address.get(), s_commitment, s_id);
    }

    function transferVaultContent(address dest) public view onlyFrom(s_auction){
        uint128 grams = 10000;
        IVault(vault_address.get()).transfer{
                value: 0,
                flag: 128
            }(dest, s_commitment, grams);
    }
}