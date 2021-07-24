

interface ITONTokenWallet {


    struct ITONTokenWalletDetails {
        address root_address;
        uint256 wallet_public_key;
        address owner_address;
        uint128 balance;

        address receive_callback;
        address bounced_callback;
        bool allow_non_notifiable;
    }
    function getDetails() external view responsible returns (ITONTokenWalletDetails);

  
    function setReceiveCallback(address receive_callback,
                                bool allow_non_notifiable) external;

    function transfer(
        address to,
        uint128 tokens,
        uint128 grams,
        address send_gas_to,
        bool notify_receiver,
        TvmCell payload
    ) external;

    function destroy(
        address gas_dest
    ) external ;
}
