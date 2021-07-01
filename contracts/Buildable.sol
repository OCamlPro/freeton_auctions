pragma ton-solidity >=0.44;

import "IBuildable.sol";

contract Buildable is IBuildable {
    function thisIsMyCode() external override responsible returns(TvmCell){
        tvm.accept();
        return tvm.code();
    }
}