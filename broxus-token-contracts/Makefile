

all: contracts
	ft contract import RootTokenContract.sol -f
	ft contract import TONTokenWallet.sol -f

contracts: RootTokenContract.tvm TONTokenWallet.tvm

RootTokenContract.tvm: RootTokenContract.sol
	ft contract build RootTokenContract.sol -f --contract RootTokenContract


TONTokenWallet.tvm: TONTokenWallet.sol
	ft contract build TONTokenWallet.sol -f --contract TONTokenWallet

clean:
	rm -f *.code

distclean: clean
	rm -f *.tvm *.abi.json *~
