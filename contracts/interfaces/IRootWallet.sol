pragma ton-solidity >=0.44;

interface IRootWallet{
    function getWalletAddress(int8 workchainId, uint256 pubkey) external responsible returns(address);
}