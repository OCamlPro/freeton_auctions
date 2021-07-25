# Free TON On-line Auctions

See the [Submission PDF](submission.pdf) for detailed information.

## Overview
 	
Our submission is in two complementary parts, `first-version/` and
`second-version/`.

Note that a “classical error” is to implement reverse auctions as a simple change in the direction of auctions, i.e. English auctions are moving up, while Reverse English auctions are moving down. Instead, reverse auctions also reverse the position of buyers and sellers. We did this error in the `first-version/` (so we do not claim implementation of reverse auctions in that part), but correctly implemented them in the `second-version/` (but we didn’t have enough time to finish that version with debot and testing).

### Part `first-version/`

This part contains:

* A set of smart contracts in Solidity implementing various flavors of on-line auctions:

  * An `AuctionRoot` contract used to easily deploy the different auction flavors
  * An `EnglishAuction` contract
  
  * A `DutchAuction` contract
  
* `Bid` and `BlindBid` contracts to bid in these auctions

* All these auctions work on a generic interface for TIP-3 tokens described in the IVault interface.

* Deployment scripts using `ft`, our FreeTON wallet for developers, to test the contracts

* A formal specification of each auction in TLA+ (`tla+/`)

* A high-level specification in an UML fashion (`spec/`)

* A debot for interacting with the SC framework (`contracts/debot/`)

with the following limitations:

* Limited checks on accesses to public methods of contracts

* Reverse counterparts of the different flavors of auctions are incorrect, because the buyers and the sellers have not been reversed

### Part `second-version/`

This part complements the first-version/ part with a focus on:

* Using direct TON transfers and standard TIP-3 tokens (we used Broxus TIP-3 token contracts)

* In the “direct” flavor, the winner (buyer) “wins” control over the auction smart contract, allowing him to control the “merchandise” for the auctioneer (seller), usually, another TIP-3 token wallet. No specific method is used to bid, a simple transfer is used to bid both for TONs and TIP-3 tokens.

* In the “reverse” flavor, the winner (seller) receives the tokens (TONs or TIP-3 token) from the auctioneer (buyer), while the “merchandise” (another TIP-3 token)  is transferred from his bid contract vault to the auctioneer vault. Note that the bidder can only start bidding after transferring his merchandise to the bid contract vault, so that the merchandise is in an “escrow”.

* Particular attention has been paid on access control

The following flavors have been implemented in this model:

* English auctions (with min-increment percentage)

* Dutch auctions in automatic mode : the price decreases automatically with time

* Dutch auctions in manual mode : the price is decreased manually by the “auction house”

* Reverse English auctions

Limitations:

* No debot
* No deployment
