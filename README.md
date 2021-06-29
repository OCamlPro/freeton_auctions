# Freeton auction

This project contains:
- the TLA+ specification of the auctions (`tla+/`)
- the source code of the contracts (`contracts/`)
- a `ft` based script for deploying the infrastructure (`deploy_all.sh`)

## TLA+ Specification

The TLA+ files represent the logic behind each auction.

## Contracts

Each contract is based on the TLA+ specification. The logic behind each auction
is in the files `VEnglishAuction.sol` and `VDutchAuction.sol`, defining
abstract contracts. The actual auction contracts (`EnglishAuction.sol`,
`EnglishReverseAuction.sol`, `DutchAuction.sol` and `DutchReverseAuction.sol`)
are variations of their associated abstract contracts.

### Dutch Auction

### English Auction

## Deployment

The `deploy_all.sh` script deploys on a sandbox network the AuctionRoot contract
Example of auction deployment:

I want to start a Dutch Forward Auction with a starting price of 1000, a limit price of 200,
with a reduction of 10 every 10 seconds.

`ft multisig -a user1 --transfer 10 --to AuctionRoot deployDutchAuction '{"start_price": "1000", "end_price": "200", "price_delta":"10", "time_delta":"10"}'`

This will create and start the auction.

Once it is done, check the address of the newly created contract with

`ft inspect --past AuctionRoot`

```
IN MESSAGE:
    {
      "id": "bd7e28359ea53bda6ae69ab18ade45ffafac4d0846ee7473698496d78f8f5245",
      "dst": "0:7c0f693bf6046d7d2c5d11b7388c9947a639c813e70097c3542acf1e2b4492fe (AuctionRoot AuctionRoot/6)",
      "fwd_fee": "1181343",
      "src": "0:f89872394a383dc289f27ded48f02a6269e19d02be5821ba8081c67a1070588a (user1 SetcodeMultisigWallet2)",
      "value": "10000000000"
    }
    CALL: Input deployDutchAuction {"start_price":"1000","end_price":"200","price_delta":"10","time_delta":"0x000000000000000000000000000000000000000000000000000000000000000a"}

  OUT MESSAGE:
    {
      "id": "f00841e2e2e36e7755e731002d50780643eb98f1b46f7f1dfc713f71fd9fc844",
      "dst": "0:2d47980f4c53cea41a872e65fed0fe11d8de203b48a47dfd9dddccdb716e60f4",
      "fwd_fee": "9326072",
      "src": "0:7c0f693bf6046d7d2c5d11b7388c9947a639c813e70097c3542acf1e2b4492fe (AuctionRoot AuctionRoot/6)",
      "value": "4986011000"
    }
  OUT MESSAGE:
    {
      "id": "3a21446901ed9a7fe2e05917f38ed56f94c7280f624ee95ad91b0a1e304bd9ac",
      "msg_type_name": "ExtOut",
      "src": "0:7c0f693bf6046d7d2c5d11b7388c9947a639c813e70097c3542acf1e2b4492fe (AuctionRoot AuctionRoot/6)"
    }
```

Here, the address of the auction is `0:2d47980f4c53cea41a872e65fed0fe11d8de203b48a47dfd9dddccdb716e60f4`.
For `ft` to be able to call the contract, I must associate the ABI to the address

`ft account 0:2d47980f4c53cea41a872e65fed0fe11d8de203b48a47dfd9dddccdb716e60f4 --contract DutchAuction`

Since the time I created the contract, 10 seconds have passed, which means the price has been reduced of 10.
Let's buy !

`ft multisig -a user1 --transfer 990 --to 0:2d47980f4c53cea41a872e65fed0fe11d8de203b48a47dfd9dddccdb716e60f4 bid`

```
  IN MESSAGE:
    {
      "id": "923b1f22053b18d14ae6d041ecaeef9b8f15731c819a315c41dbeb733f0530f1",
      "dst": "0:2d47980f4c53cea41a872e65fed0fe11d8de203b48a47dfd9dddccdb716e60f4",
      "fwd_fee": "754673",
      "src": "0:f89872394a383dc289f27ded48f02a6269e19d02be5821ba8081c67a1070588a (user1 SetcodeMultisigWallet2)",
      "value": "990000000000"
    }
  OUT MESSAGE:
    {
      "id": "d065c6b5e85318c50226a8c2eb391ebf993aceb73b51a4f6307877de9375bcee",
      "bounce": false,
      "bounced": true,
      "dst": "0:f89872394a383dc289f27ded48f02a6269e19d02be5821ba8081c67a1070588a (user1 SetcodeMultisigWallet2)",
      "fwd_fee": "666672",
      "src": "0:2d47980f4c53cea41a872e65fed0fe11d8de203b48a47dfd9dddccdb716e60f4",
      "value": "989994862000"
    }
```

The value of the OUT MESSAGE represents the bid, minus the fees.