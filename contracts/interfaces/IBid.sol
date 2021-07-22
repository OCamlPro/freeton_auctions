pragma ton-solidity >=0.44;

interface IBid {
    function checkVault() external;
    function transferVaultContent(address, uint256) external;
}