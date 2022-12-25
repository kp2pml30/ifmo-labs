insert into Sessions
select (select coalesce(max(SessionId), 1) from Sessions) + TeamId as SessionId, TeamId, :ContestId as ContestId, current_timestamp as Start
from Teams
where TeamId not in (select TeamId from Sessions where ContestId = :ContestId)