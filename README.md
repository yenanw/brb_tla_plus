# Model Checking BRB in TLA+

Byzantine Reliable Broadcast or BRB is a broadcast algorithm that ensures reliable delivery of messages to all process in a network, even under the presence of Byzantine nodes (malicious actors that can behave arbitrarily).

This repository contains TLA+/PlusCal specifications for various BRB algorithms. 

Currently the following BRB algorithms are implemented:

- **Bracha's BRB** - The foundantional asynchrous BRB protocol
  - **Threshold:** $n > 3 \cdot t$
  - **Reference:** Originally from [Bracha (1987)](https://doi.org/10.1016/0890-5401(87)90054-X), we use the version defined in Section 4.4 of [the book by M. Raynal](https://link.springer.com/book/10.1007/978-3-319-94141-7).

## Project Structure

All specifications are placed in the `specs/[BRB name]/` directory, which includes the `.tla` and `.cfg` files.

The `.tla` files contains the BRB specification, while `.cfg` files are the configs used by [TLC](https://docs.tlapl.us/using:tlc:start) for model checking. 

## How to Run 

While the [TLA+ Toolbox](https://lamport.azurewebsites.net/tla/toolbox.html) can be used to run the specifications, we recommended using the [VSCode extension](https://github.com/tlaplus/vscode-tlaplus) of TLA+ instead for convenience.

- Install the [TLA+ VSCode extension](https://github.com/tlaplus/vscode-tlaplus).
- Modify the model as desired in the corresponding `.cfg` file.
- Open the `.tla` file and run the command `TLA+: check model with TLC` in the command palette (opened using `Ctrl+Shift+p`) to start model checking with TLC.
- If you have modified PlusCal specification in the `.tla` file, then make sure to run `TLA+: parse module` before model checking.