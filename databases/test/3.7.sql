insert into Sessions
select (select coalesce(max(SessionId), 1) from Sessions) + TeamId as SessionId, TeamId, :ContestId as ContestId, current_timestamp as Start
from Teamsasdasdasdasdasd
on conflict (TeamId, ContestId) do
	update set Start = current_timestamp