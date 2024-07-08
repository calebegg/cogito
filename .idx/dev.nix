# To learn more about how to use Nix to configure your environment
# see: https://developers.google.com/idx/guides/customize-idx-env
{ pkgs, ... }: {
  # Which nixpkgs channel to use.
  channel = "stable-23.11"; # or "unstable"
  # Use https://search.nixos.org/packages to find packages
  packages = [
  ];
  # Sets environment variables in the workspace
  env = {};
  idx = {
    extensions = [
      "denoland.vscode-deno"
      "ms-vscode.live-server"
      "ryanluker.vscode-coverage-gutters"
    ];
    # Workspace lifecycle hooks
    workspace = {
      # Runs when a workspace is first created
      onCreate = {
        deno-install = "curl -fsSL https://deno.land/install.sh | sh";
        deno-path-add = "echo 'PATH=$PATH:~/.deno/bin >> ~/.bashrc";
      };
      # Runs when the workspace is (re)started
      onStart = {
        # Example: start a background task to watch and re-build backend code
        # watch-backend = "npm run watch-backend";
      };
    };
  };
}
