# adaptive_subtraction

### Install Dependencies

```
winget install -e --id Git.Git --source winget --silent --accept-package-agreements --accept-source-agreements --disable-interactivity
$installCode = (Invoke-WebRequest -Uri "https://elan.lean-lang.org/elan-init.ps1" -UseBasicParsing -ErrorAction Stop).Content
$installer = [ScriptBlock]::Create([System.Text.Encoding]::UTF8.GetString($installCode))
Set-ExecutionPolicy -ExecutionPolicy Unrestricted -Scope Process
& $installer -NoPrompt 1 -DefaultToolchain ${elanStableChannel}
```



Install Scoop

```powershell
Set-ExecutionPolicy -ExecutionPolicy RemoteSigned -Scope CurrentUser
Invoke-RestMethod -Uri https://get.scoop.sh | Invoke-Expression
```

```powershell
scoop bucket add main
scoop install main/elan
```

```powershell
elan toolchain install leanprover/lean4:nightly
elan default leanprover/lean4:nightly
```

$env:PATH = "$env:PATH;C:\Users\Chris\scoop\apps\elan\current\.elan\bin\"


[System.Environment]::SetEnvironmentVariable(
    'PATH',
    "$([System.Environment]::GetEnvironmentVariable('PATH','User'));C:\Users\Chris\scoop\apps\elan\current\.elan\bin\",
    'User'
)




Install Chocolatey if you need it
```powershell
iwr https://community.chocolatey.org/install.ps1 -UseBasicParsing | iex
```

Install L∃∀N
```powershell
choco install lean
```

Install WSL
```powershell
wsl --install
```

Install Docker 
```powershell
winget install -e --id Docker.DockerDesktop
```

Restart Terminal, install lean dependencies

```powershell
lake update
```

# Clone Repo
```powershell
git clone https://github.com/sav-chris/AdaptiveSubtractionProofs.git

cd AdaptiveSubtractionProofs/proofs
```

# Running in Docker

Start Docker desktop

Start the container
```powershell
docker compose up
```

# Running Locally 

```powershell
lake update
lake exe cache get
```

```powershell
lake build
```
