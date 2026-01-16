# Lean 4 环境准备（Windows & macOS）

第一次上手 Lean 4 只需要做三件事：  
1. 让系统能找到编译器（靠 elan）；  
2. 让编辑器能实时对话编译器（靠 VS Code 插件）；  
3. 把数学库 mathlib4 准备妥当（靠 lake）。  
   
下面给出`Windows/macOS`系统的环境准备操作。

---

## 1. 共用前置：VS Code 与 Git
无论哪个平台，Lean 4 的官方插件都只认 VS Code，而依赖下载又全靠 Git，所以这两样必须提前就位。

1. 安装 VS Code  
   官网 [https://code.visualstudio.com](https://code.visualstudio.com) 一路“下一步”安装，**Windows 用户请勾选“添加到 PATH”**，macOS 用户无需额外设置。

2. 安装 Git  
   - Windows：到 [Git for Windows](https://git-scm.com/download/win) 下载，安装器会连问 7–8 个问题，**唯一需要改动的是默认编辑器**，从 vim 改成 VS Code，其余保持默认即可；装完后在 PowerShell 执行一次  
     ```powershell
     git config --global core.autocrlf input
     ```  
     防止 Windows 行尾符号 `\r\n` 被 Lean 当成非法字符。  
   - macOS：系统已自带 Git，可跳过；若曾装过 Homebrew 版 Git 也无需额外配置。

---

## 2. 安装 Lean 工具链（elan + lake + lean）
elan 是“版本管理器”，lake 是“构建工具”，lean 是“编译器”。  
官方把三者做成了一键脚本，但 Windows 与 macOS 的下载入口不同。

### Windows（PowerShell 管理员权限）
1. 以**管理员身份**打开 PowerShell，复制执行：
   ```powershell
   powershell -ExecutionPolicy Bypass -c "iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex"
   ```
2. 脚本会在 `%USERPROFILE%\.elan` 放下 `elan`，并自动把 `lean`、`lake` 加入用户 PATH。
3. 出现 `Elan installed successfully` 后，关闭当前 `PowerShell` 再重新打开，让 PATH 生效。
   
### macOS（bash）
1. 打开 Terminal，复制执行：
   ```bash
    /bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/leanprover-community/mathlib4/master/scripts/install_macos.sh)" && source ~/.profile
   ```
2. 脚本会调用 `Homebrew` 安装或更新 `elan`，并把可执行文件软链到 `/usr/local/bin`。
3. 若关闭终端后再开出现 `lean: command not found`，执行 `source ~/.profile` 或干脆重新登录一次系统即可。

---

## 3. VS Code 插件

1. 启动 VS Code → 左侧扩展图标 → 搜索 lean4 → 安装 Lean 4 (leanprover.lean4)。
2. 新建文件，保存为 `test.lean`，输入：
    ```lean
    #eval 1 + 1
    ```
    - 若右下角自动弹出 `Lean Infoview` 并显示 2，说明语言服务器已启动。
    - 若提示 `Lean 4 server not found`，99% 是 PATH 未刷新，重启 VS Code 即可；仍失败就手动在命令面板（`Ctrl+Shift+P` / `Cmd+Shift+P`）执行 `Lean 4: Select Toolchain` → 选 `stable`。

---

## 4. Mathlib4 库及项目测试

Lean 的数学库体积较大，提前跑一次可避免正式使用时卡壳。

```bash
# 终端中在任意空白文件夹执行
lake new hello_math math   # 生成带 mathlib 依赖的标准项目
cd hello_math
lake exe cache get         # 先拉GitHub上提前编译好的 .olean 等缓存文件，如果跳过这一步会进行本地编译，时间会长很多
lake build                 # 自动 git clone + 编译
```

看到 `✔ Build completed` 即网络与缓存都就绪；若因网络问题卡在git clone，需要检查网络或再次尝试。