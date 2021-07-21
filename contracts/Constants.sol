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
    uint16 constant E_FAILED_REVELATION = 110;
    uint16 constant E_NO_NEXT_BID = 111;

}