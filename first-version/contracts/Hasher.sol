pragma ton-solidity >=0.44;

contract Hasher {
    function hash(uint256 salt, uint256 amount) pure public returns(uint256){
        uint256 h_salt = tvm.hash(format("{}",salt));
        uint256 h_amount = tvm.hash(format("{}",amount));
        return (tvm.hash(format("{}",h_salt + h_amount)));
    }
}