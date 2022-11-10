{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    flake-utils = {
      url = "github:numtide/flake-utils";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { nixpkgs, flake-utils, ... }: flake-utils.lib.eachDefaultSystem (system:
    let pkgs = import nixpkgs { inherit system; };
        lua = (pkgs.lua5_4.withPackages(ps: with ps; [ lpeg lpeg_patterns lpeglabel ]));
    in {
      devShells.default = pkgs.mkShell {
        nativeBuildInputs = with pkgs; [ lua llvm clang clang-tools ];
      };
    }
  );
}

