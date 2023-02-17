Task.Supervisor.start_link(name: Main.TaskSupervisor)

defmodule Main do
  def doTask(query, servers) do
    master = Task.async(fn ->
      # clild actor
      childFn = fn (server) -> fn ->
        receive do
          {sender, :query, query} ->
            [0, 1, 2]
            |> Enum.each(fn i ->
              send sender, {:ans, server.(query, i)}
            end)
            send sender, {:done}
        end
      end end

      # make children for each search engine
      children =
        servers
        |> Enum.map(childFn)
        |> Enum.map(&Task.Supervisor.async_nolink(Main.TaskSupervisor, &1))
      Enum.each(children, fn c -> send(c.pid, {self(), :query, query}) end)

      # await and aggregate/main actor callback
      start = :os.system_time(:millisecond)
      popper = fn ({rest, lst}, rec) ->
        receive do
          {:ans, q} ->
            rec.({rest, [q | lst]}, rec)
          {:done} ->
            if rest == 1 do
              lst
            else
              rec.({rest - 1, lst}, rec)
            end
        after Enum.max([0, 5000 - (:os.system_time(:millisecond) - start)]) -> lst
        end
      end
      ans = popper.({length(children), []}, popper) |> Enum.reverse
      children |> Enum.each(&Task.shutdown(&1, :brutal_kill))
      ans
    end)

    # run master
    Task.await(master, :infinity)
  end

  def main(_ \\ []) do
    doTask("abc", ["y", "g", "b"] |> Enum.map(fn id -> fn (x, i) -> :timer.sleep(:rand.uniform(500)); "answer#{i} for #{x} from #{id}" end end))
      |> Enum.with_index
      |> Enum.each(fn({x, i}) ->
        IO.puts("# #{i}. #{x}")
      end)
  end

end

Main.main()

ExUnit.start()
defmodule MainTest do
  use ExUnit.Case, async: true

  def formater(id, x, i) do
    "answer#{i} for `#{x}` from #{id}"
  end

  def servs(slp) do
    ["y", "g", "b"] |> Enum.map(fn id -> fn (x, y) -> :timer.sleep(slp); MainTest.formater(id, x, y) end end)
  end


  test "instant" do
    Task.Supervisor.start_link(name: Main.TaskSupervisor)
    a1 = Main.doTask("abc", servs(0))
    a2 = ["y", "g", "b"]
      |> Enum.flat_map(fn id ->
        [0, 1, 2]
          |> Enum.map(fn i -> MainTest.formater(id, "abc", i) end)
      end)
    assert Enum.sort(a1) == Enum.sort(a2)
  end

  test "long" do
    Task.Supervisor.start_link(name: Main.TaskSupervisor)
    a1 = Main.doTask("abc", servs(4000))
    a2 = ["y", "g", "b"]
      |> Enum.flat_map(fn id ->
        [0]
          |> Enum.map(fn i -> MainTest.formater(id, "abc", i) end)
      end)
    assert Enum.sort(a1) == Enum.sort(a2)
  end

  test "med" do
    Task.Supervisor.start_link(name: Main.TaskSupervisor)
    a1 = Main.doTask("abc", servs(2000))
    a2 = ["y", "g", "b"]
      |> Enum.flat_map(fn id ->
        [0, 1]
          |> Enum.map(fn i -> MainTest.formater(id, "abc", i) end)
      end)
    assert Enum.sort(a1) == Enum.sort(a2)
  end

  test "never" do
    Task.Supervisor.start_link(name: Main.TaskSupervisor)
    a1 = Main.doTask("abc", servs(999999))
    assert a1 == []
  end
end
