pragma ton-solidity >=0.44;

import "IVault.sol";
import "Constants.sol";

contract CrystalVault is IVault, Constants{
    
    address static s_process_winner_address;

    modifier onlyFrom(address addr){
        require (msg.sender == addr, E_UNAUTHORIZED);
        _;
    }

    constructor() public{
        tvm.accept();
    }

    function transfer(address dest, uint256 tokens, uint128 grams) external override onlyFrom(s_process_winner_address){
        uint128 to_transfer;
        if (tokens >= address(this).balance - grams) {
            // This test ensures what is sent is lower than 2^128
            to_transfer = address(this).balance - grams;
        } else {
            to_transfer = uint128(tokens);
        }
        dest.transfer({value: to_transfer, flag: 0});
    }

    function getBalance() responsible external override returns(uint256){
        return {value:0, flag: 128} address(this).balance;
    }

}