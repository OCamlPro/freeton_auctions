
interface IRootTokenContract {

    function deployEmptyWallet(
        uint128 deploy_grams,
        uint256 wallet_public_key,
        address owner_address,
        address gas_back_address
    ) external returns(address);

    function getWalletAddress(uint256 wallet_public_key,
                              address owner_address)
      external view responsible returns(address);

}
