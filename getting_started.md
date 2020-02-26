# Getting started

You can create `.bm` (machine) and `.bc` (context) files at the root of this directory.

Everytime you save, the files will be compiled into a Rodin-friendly XML, in the `./rodin-project` directory.

## First time setup

1. Open Rodin in the current directory

    - In Visual Studio: `View` > `Command Palette` (shortcut `CTRL+SHIFT+P`) and search the command `[Event-B] Run in Rodin Platform`.

2. Import the `rodin-project`. This should only be done the first time: afterwards, the workspace will remember that you imported the project.

    - In Rodin: Right click on the Event-B Explorer > `Import`. A window opens.

    - Select `General` > `Existing Projects into Workspace` and hit Next.

    - In `Select root directory`, click on `Browse` and select the `rodin-project` folder.

    - Select `Finish`. You should see your project and your machines/contexts.



## How to use ?

- Edit your `.bm` and `.bc` files in VSCode.

- When you feel like testing, save the file and hit `F5` in the Rodin Editor to refresh the XML.

- You can now use Rodin and ProB to test your files !

## What are the benefits of this method ?

- Avoid Rodin editor
- Avoid Camille editor
- Get some snippets
- Write symbols in a more intuitive manner
- You can use this git repository without worrying about conflicts due to the XML
- Avoid Rodin editor
- Dark mode
- You can use VSCode shortcuts, multi-cursors, etc...
- Less bugs (I hope)
- AVOID RODIN EDITOR