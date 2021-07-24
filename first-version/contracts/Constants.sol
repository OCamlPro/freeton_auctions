pragma ton-solidity >=0.44;

import "interfaces/IConstants.sol";

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

    modifier onlyFrom(address a){
        require(msg.sender == a, E_UNAUTHORIZED);
        _;
    }

}